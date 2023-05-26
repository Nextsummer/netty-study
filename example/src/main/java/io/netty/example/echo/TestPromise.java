package io.netty.example.echo;

import io.netty.channel.nio.NioEventLoopGroup;
import io.netty.util.concurrent.DefaultPromise;
import io.netty.util.concurrent.GenericFutureListener;
import io.netty.util.concurrent.Promise;
import io.netty.util.concurrent.Future;

import java.util.concurrent.Callable;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.TimeUnit;

/**
 * <B>主类名称：</B>Demo<BR>
 * <B>概要说明：</B><BR>
 *
 * @author SunJing
 * @since 2023-05-25 23:35
 */
public class TestPromise {


    public static void main(String[] args) throws ExecutionException, InterruptedException {
        TestPromise testPromise = new TestPromise();
        Promise<String> promise = testPromise.queryUserInfo("10001");
        promise.addListener(new GenericFutureListener<Future<? super String>>() {
            @Override
            public void operationComplete(Future<? super String> future) throws Exception {
                System.out.println("addListener.operationComplete > 查询用户信息完成： " + future.get());
            }
        });
    }

    private Promise<String> queryUserInfo(final String userId) {
        NioEventLoopGroup loop = new NioEventLoopGroup();
        // 创建一个DefaultPromise并返回，将业务逻辑放入线程池中执行
        final DefaultPromise<String> promise = new DefaultPromise<String>(loop.next());
        loop.schedule(new Callable<Object>() {
            @Override
            public Object call() throws Exception {
                try {
                    Thread.sleep(1000);
                    promise.setSuccess("微信公众号：bugstack虫洞栈 | 用户ID：" + userId);
                    return promise;
                } catch (InterruptedException ignored) {
                }
                return promise;
            }
        }, 10, TimeUnit.SECONDS);
        return promise;
    }
}
